package com.example.backend.business.entities;

import java.util.Date;
import java.util.Optional;

public class AssignmentDTO {
    private Long id;
    private String title;
    private String description;
    private Long courseId;
    private Optional<Date> dueDate;

    public AssignmentDTO() {

    }

    public AssignmentDTO(Long id, String title, String description, Long courseId, Optional<Date> dueDate) {
        this.id = id;
        this.title = title;
        this.description = description;
        this.courseId = courseId;
        this.dueDate = dueDate;
    }

    public Long getId() {
        return id;
    }

    public void setId(Long id) {
        this.id = id;
    }

    public String getTitle() {
        return title;
    }

    public void setTitle(String title) {
        this.title = title;
    }

    public String getDescription() {
        return description;
    }

    public void setDescription(String description) {
        this.description = description;
    }

    public Long getCourseId() {
        return courseId;
    }

    public void setCourseId(Long courseId) {
        this.courseId = courseId;
    }

    public Optional<Date> getDueDate() {
        return dueDate;
    }

    public void setDueDate(Optional<Date> dueDate) {
        this.dueDate = dueDate;
    }
}
