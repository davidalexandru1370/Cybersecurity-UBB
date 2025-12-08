package com.example.backend.business.entities;

import java.util.Optional;

import io.micrometer.common.lang.NonNull;

public class CreateAssignmentDTO {
    private String title;
    private String description;
    private Long courseId;
    private Optional<Long> dueDate; // Unix timestamp

    public CreateAssignmentDTO() {
    }

    public CreateAssignmentDTO(String title, String description, @NonNull Long courseId, Optional<Long> dueDate) {
        this.title = title;
        this.description = description;
        this.courseId = courseId;
        this.dueDate = dueDate;
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

    public Optional<Long> getDueDate() {
        return dueDate;
    }

    public void setDueDate(Optional<Long> dueDate) {
        this.dueDate = dueDate;
    }

    public Long getCourseId() {
        return courseId;
    }
}
