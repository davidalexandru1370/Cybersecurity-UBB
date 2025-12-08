package com.example.backend.business.entities;

import java.util.Optional;

public class AssignmentDTO {
    private Long id;
    private String title;
    private String description;
    private Long courseId;
    private Optional<Long> dueDate;
    private Optional<Float> grade;
    private Optional<String> feedback;

    public AssignmentDTO() {

    }

    public AssignmentDTO(Long id, String title, String description, Long courseId, Optional<Long> dueDate,
            Optional<Float> grade, Optional<String> feedback) {
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

    public Optional<Long> getDueDate() {
        return dueDate;
    }

    public void setDueDate(Optional<Long> dueDate) {
        this.dueDate = dueDate;
    }

    public Optional<Float> getGrade() {
        return grade;
    }

    public Optional<String> getFeedback() {
        return feedback;
    }
}
